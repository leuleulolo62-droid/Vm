-- ===== Key System (must pass before the script runs) =====
local function __y2k_keygate()
-- ============================================================================
--  Y2k key provider  (drop-in replacement for the Junkie SDK)
--  Talks to YOUR Cloudflare Worker + KV key server (server-side hashing, HWID
--  auto-bind, expiry). CONFIGURE the two URLs below. Server: server-example/.
-- ============================================================================
local Junkie = {}
do
	local KEY_API  = "https://y2k-keys.y2kscript.workers.dev"  -- your deployed Worker (LIVE)
	local KEY_LINK = "https://work.ink/2Dgt/ks-int12887-kq76mlra7lo" -- work.ink key link

	local HttpService = game:GetService("HttpService")
	local function enc(s) local ok, r = pcall(function() return HttpService:UrlEncode(s) end) return ok and r or s end
	local function httpGet(u)
		for _, f in ipairs({
			function() return game:HttpGetAsync(u) end,
			function() return game:HttpGet(u) end,
			function() return request and request({ Url = u, Method = "GET" }).Body end,
		}) do
			local ok, b = pcall(f); if ok and type(b) == "string" then return b end
		end
		return nil
	end
	local function hwid()
		local id
		pcall(function() id = (gethwid and gethwid()) or (get_hwid and get_hwid()) end)
		if not id then pcall(function() id = game:GetService("RbxAnalyticsService"):GetClientId() end) end
		return tostring(id or "unknown")
	end

	function Junkie.get_key_link() return KEY_LINK end
	function Junkie.check_key(key)
		if not key or key == "" then return { valid = false, message = "No key entered" } end
		local hw = hwid()
		local url = KEY_API .. "/check?key=" .. enc(key) .. "&hwid=" .. enc(hw) .. "&t=" .. tostring(os.time())
		local body = httpGet(url)
		if not body then return { valid = false, message = "Key server unreachable" } end
		local b = string.lower(body)
		if string.find(b, "ok", 1, true) then
			getgenv().HWID = hw
			return { valid = true, message = "KEY_VALID", hwid = hw }
		elseif string.find(b, "expired", 1, true) then
			return { valid = false, message = "Key expired" }
		elseif string.find(b, "hwid", 1, true) then
			return { valid = false, message = "Key locked to another device" }
		else
			return { valid = false, message = "Invalid key" }
		end
	end
end


local TweenService = game:GetService("TweenService")
local UserInputService = game:GetService("UserInputService")
local RunService = game:GetService("RunService")
local Players = game:GetService("Players")
local Lighting = game:GetService("Lighting")
local HttpService = game:GetService("HttpService")

local Icons = {
	Shield = "rbxassetid://105619007041452",
	Loading = "rbxassetid://116535712789945",
	Lock = "rbxassetid://114355063515473",
	Key = "rbxassetid://93569468678423",
	Check = "rbxassetid://119783053916823",
	CheckCircle = "rbxassetid://10709790644",
	XCircle = "rbxassetid://10747384394",
	Warning = "rbxassetid://130226573962640",
	Globe = "rbxassetid://10734950309",
	Info = "rbxassetid://94529541997278",
	ExternalLink = "rbxassetid://71038734318580",
	Copy = "rbxassetid://107485544510830",
	Spinner = "rbxassetid://10709767827",
	Database = "rbxassetid://114209748010261",
	Sparkles = "rbxassetid://10709767827",
	ErrorFolder = "rbxassetid://113312905787220",
	Candy = "rbxassetid://10709767827",
	JunkieNewIcon = "rbxassetid://75038032192167"
}

local function hasFileSystemSupport()
    local hasWritefile = pcall(function() return type(writefile) == "function" end)
    local hasReadfile = pcall(function() return type(readfile) == "function" end)
    local hasIsfile = pcall(function() return type(isfile) == "function" end)
    return hasWritefile and hasReadfile and hasIsfile
end

local fileSystemSupported = hasFileSystemSupport()

local function saveVerifiedKey(key)
    if not fileSystemSupported then return false end
    local ok = pcall(function()
        writefile("verified_key.txt", key)
    end)
    return ok
end

local function loadVerifiedKey()
    if not fileSystemSupported then 
        return nil 
    end
    
    local ok, content = pcall(function()
        return readfile("verified_key.txt")
    end)
    
    if not ok or not content then 
        return nil 
    end
    return content
end

local function clearSavedKey()
    if not fileSystemSupported then return false end
    local ok = pcall(function() delfile("verified_key.txt") end)
    return ok
end

local Configuration = {
	ScreenGuiName = "JunkieKeySystem",
	Window = {Size = UDim2.new(0, 333, 0, 500)},
	Colors = {
		Bg = Color3.fromRGB(12, 12, 12),
		Primary = Color3.fromRGB(59, 130, 246),
		PrimaryDark = Color3.fromRGB(37, 99, 235),
		StatusIdle = Color3.fromRGB(249, 115, 22),
		StatusSuccess = Color3.fromRGB(16, 185, 129),
		StatusError = Color3.fromRGB(239, 68, 68),
		StatusVerifying = Color3.fromRGB(59, 130, 246),
		StatusWarning = Color3.fromRGB(254, 188, 46),
		TextMain = Color3.fromRGB(255, 255, 255),
		TextSec = Color3.fromRGB(161, 161, 170),
		TextMuted = Color3.fromRGB(113, 113, 122),
		Border = Color3.fromRGB(255, 255, 255),
		TrafficRed = Color3.fromRGB(255, 95, 87),
		TrafficYellow = Color3.fromRGB(254, 188, 46),
		TrafficGreen = Color3.fromRGB(40, 200, 64),
		Success = Color3.fromRGB(50, 205, 110),
		Error = Color3.fromRGB(245, 70, 90),
		Warning = Color3.fromRGB(255, 200, 50)
	},
	BorderTransparency = 0.15,
	Animations = {
		VeryFast = 0.1,
		Fast = 0.2,
		Medium = 0.4,
		Slow = 0.5,
		VerySlow = 0.6,
		Bounce = 0.6
	},
	Fonts = {
		Title = 24,
		Subtitle = 12,
		Button = 14,
		Input = 16,
		Body = 13,
		Small = 11,
		Tiny = 12
	}
}

local Utils = {}

Utils.Tween = function(obj, props, time, style, dir)
	local t =
		TweenService:Create(
		obj,
		TweenInfo.new(time or 0.3, style or Enum.EasingStyle.Quint, dir or Enum.EasingDirection.Out),
		props
	)
	t:Play()
	return t
end

Utils.CreateCorner = function(parent, radius)
	local corner = Instance.new("UICorner")
	corner.CornerRadius = UDim.new(0, radius or Configuration.CornerRadius)
	corner.Parent = parent
	return corner
end

Utils.Round = function(obj, radius)
	local c = Instance.new("UICorner")
	c.CornerRadius = UDim.new(0, radius or 12)
	c.Parent = obj
	return c
end

Utils.TweenBack = function(instance, properties, duration)
	return Utils.Tween(instance, properties, duration, Enum.EasingStyle.Back, Enum.EasingDirection.Out)
end

Utils.CreateStroke = function(parent, color, thickness, transparency)
	local stroke = Instance.new("UIStroke")
	stroke.Color = color or Configuration.Colors.Border
	stroke.Thickness = thickness or 1
	stroke.Transparency = transparency or 0.77
	stroke.ApplyStrokeMode = Enum.ApplyStrokeMode.Border
	stroke.Parent = parent
	return stroke
end

Utils.Stroke = function(obj, color, thick, trans)
	local s = Instance.new("UIStroke")
	s.Color = color or Color3.new(1, 1, 1)
	s.Thickness = thick or 1
	s.Transparency = trans or 0.9
	s.ApplyStrokeMode = Enum.ApplyStrokeMode.Border
	s.Parent = obj
	return s
end

Utils.CreateGradient = function(parent, color1, color2, rotation)
	local gradient = Instance.new("UIGradient")
	gradient.Color =
		ColorSequence.new(
		{
			ColorSequenceKeypoint.new(0, color1),
			ColorSequenceKeypoint.new(1, color2)
		}
	)
	gradient.Rotation = rotation or 300
	gradient.Parent = parent
	return gradient
end

local function SetBlur(enabled)
	local blur = Lighting:FindFirstChild("JunkieBlur")
	if enabled then
		if not blur then
			blur = Instance.new("BlurEffect")
			blur.Name = "JunkieBlur"
			blur.Size = 0
			blur.Parent = Lighting
		end
		Utils.Tween(blur, {Size = 24}, Configuration.Animations.Bounce)
	elseif blur then
		Utils.Tween(blur, {Size = 0}, Configuration.Animations.Medium)
		task.delay(
			0.4,
			function()
				blur:Destroy()
			end
		)
	end
end

local ToastSystem = {ActiveToasts = {}, MaxToasts = 3, ToastSpacing = 10}

ToastSystem.Create = function(parent, message, toastType, duration, statusCode)
	local colors = {
		success = Configuration.Colors.Success,
		error = Configuration.Colors.Error,
		warning = Configuration.Colors.Warning,
		info = Configuration.Colors.Primary
	}
	local icons = {
		success = Icons.CheckCircle,
		error = Icons.ErrorFolder,
		warning = Icons.Warning,
		info = Icons.Info
	}
	local toastColor = colors[toastType] or colors.Bg
	local toastIcon = icons[toastType] or nil
	if #ToastSystem.ActiveToasts >= ToastSystem.MaxToasts then
		local oldest = table.remove(ToastSystem.ActiveToasts, 1)
		if oldest and oldest.Parent then
			oldest:Destroy()
		end
	end
	local toastHeight = 56
	local toast = Instance.new("Frame")
	toast.Name = tick()
	toast.Size = UDim2.new(0, 0, 0, toastHeight)
	toast.Position = UDim2.new(0.5, 0, 0, 20)
	toast.AnchorPoint = Vector2.new(0.5, 0)
	toast.BackgroundColor3 = Configuration.Colors.Bg
	toast.BackgroundTransparency = 0.5
	toast.BorderSizePixel = 0
	toast.ZIndex = 300
	toast.ClipsDescendants = true
	toast.Parent = parent
	Utils.Round(toast, 14)
	Utils.CreateStroke(toast, toastColor, 1, 0.1)
	Utils.CreateGradient(toast, Configuration.Colors.Bg, Configuration.Colors.Bg, 1)
	local iconBg = Instance.new("Frame")
	iconBg.Name = "IconBg"
	iconBg.Size = UDim2.new(0, 36, 0, 36)
	iconBg.Position = UDim2.new(0, 12, 0.5, 0)
	iconBg.AnchorPoint = Vector2.new(0, 0.5)
	iconBg.BackgroundColor3 = toastColor
	iconBg.BackgroundTransparency = 0.85
	iconBg.BorderSizePixel = 0
	iconBg.ZIndex = 301
	iconBg.Parent = toast
	Utils.Round(iconBg, 18)
	local icon = Instance.new("ImageLabel")
	icon.Name = "Icon"
	icon.Size = UDim2.new(0, 20, 0, 20)
	icon.Position = UDim2.new(0.5, 0, 0.5, 0)
	icon.AnchorPoint = Vector2.new(0.5, 0.5)
	icon.BackgroundTransparency = 1
	icon.Image = toastIcon
	icon.ImageColor3 = toastColor
	icon.ZIndex = 302
	icon.Parent = iconBg
	local textContainer = Instance.new("Frame")
	textContainer.Name = "TextContainer"
	textContainer.Size = UDim2.new(1, statusCode and -110 or -60, 1, 0)
	textContainer.Position = UDim2.new(0, 56, 0, 0)
	textContainer.BackgroundTransparency = 1
	textContainer.ZIndex = 301
	textContainer.Parent = toast
	local text = Instance.new("TextLabel")
	text.Name = "Message"
	text.Size = UDim2.new(1, 0, 1, 0)
	text.BackgroundTransparency = 1
	text.Text = message or ""
	text.TextColor3 = Configuration.Colors.TextMain
	text.TextSize = Configuration.Fonts.Body
	text.Font = Enum.Font.GothamMedium
	text.TextXAlignment = Enum.TextXAlignment.Left
	text.TextYAlignment = Enum.TextYAlignment.Center
	text.TextWrapped = true
	text.ZIndex = 301
	text.Parent = textContainer
	if statusCode then
		local statusBadge = Instance.new("Frame")
		statusBadge.Name = "StatusBadge"
		statusBadge.Size = UDim2.new(0, 44, 0, 28)
		statusBadge.Position = UDim2.new(1, -12, 0.5, 0)
		statusBadge.AnchorPoint = Vector2.new(1, 0.5)
		statusBadge.BackgroundColor3 = toastColor
		statusBadge.BackgroundTransparency = 0.8
		statusBadge.BorderSizePixel = 0
		statusBadge.ZIndex = 301
		statusBadge.Parent = toast
		Utils.Round(statusBadge, 8)
		Utils.CreateStroke(statusBadge, toastColor, 1, Configuration.BorderTransparency)
		local statusCodeLabel = Instance.new("TextLabel")
		statusCodeLabel.Name = "StatusCode"
		statusCodeLabel.Size = UDim2.new(1, 0, 1, 0)
		statusCodeLabel.BackgroundTransparency = 1
		statusCodeLabel.Text = tostring(statusCode)
		statusCodeLabel.TextColor3 = toastColor
		statusCodeLabel.TextSize = Configuration.Fonts.Small
		statusCodeLabel.Font = Enum.Font.GothamBold
		statusCodeLabel.ZIndex = 302
		statusCodeLabel.Parent = statusBadge
	end
	table.insert(ToastSystem.ActiveToasts, toast)
	ToastSystem.RepositionToasts()
	local targetWidth = 320
	Utils.TweenBack(toast, {Size = UDim2.new(0, targetWidth, 0, toastHeight)}, Configuration.Animations.Medium)
	task.delay(
		duration or 3.5,
		function()
			if toast.Parent then
				Utils.Tween(
					toast,
					{
						Position = UDim2.new(0.5, 0, 0, -80),
						BackgroundTransparency = 1
					},
					Configuration.Animations.Medium
				)
				for i, t in ipairs(ToastSystem.ActiveToasts) do
					if t == toast then
						table.remove(ToastSystem.ActiveToasts, i)
						break
					end
				end
				task.wait(Configuration.Animations.Medium)
				toast:Destroy()
				ToastSystem.RepositionToasts()
			end
		end
	)
	return toast
end

ToastSystem.RepositionToasts = function()
	for i, toast in ipairs(ToastSystem.ActiveToasts) do
		local targetY = 20 + ((i - 1) * (60 + ToastSystem.ToastSpacing))
		Utils.Tween(toast, {Position = UDim2.new(0.5, 0, 0, targetY)}, Configuration.Animations.Medium)
	end
end

local function Build()
	local parent = game:GetService("CoreGui")
	local old = parent:FindFirstChild(Configuration.ScreenGuiName)
	if old then
		old:Destroy()
	end
	local screen = Instance.new("ScreenGui")
	screen.Name = Configuration.ScreenGuiName
	screen.ResetOnSpawn = false
	screen.Parent = parent

	-- Discord banner (top of screen, transparent, blinking + glow)
	local discordBanner = Instance.new("TextLabel")
	discordBanner.Name = "DiscordBanner"
	discordBanner.Size = UDim2.new(0, 400, 0, 32)
	discordBanner.Position = UDim2.new(0.5, 0, 0, 10)
	discordBanner.AnchorPoint = Vector2.new(0.5, 0)
	discordBanner.BackgroundTransparency = 1
	discordBanner.Text = "Join https://discord.gg/EFFKrfFkPQ"
	discordBanner.TextColor3 = Color3.fromRGB(88, 101, 242)
	discordBanner.TextSize = 16
	discordBanner.Font = Enum.Font.GothamBold
	discordBanner.TextTransparency = 0
	discordBanner.Parent = screen

	local bannerStroke = Instance.new("UIStroke")
	bannerStroke.Color = Color3.fromRGB(88, 101, 242)
	bannerStroke.Thickness = 2
	bannerStroke.Transparency = 0.3
	bannerStroke.Parent = discordBanner

	task.spawn(function()
		while discordBanner and discordBanner.Parent do
			Utils.Tween(discordBanner, {TextTransparency = 0.4}, 0.6)
			Utils.Tween(bannerStroke, {Transparency = 0.7}, 0.6)
			task.wait(0.6)
			Utils.Tween(discordBanner, {TextTransparency = 0}, 0.6)
			Utils.Tween(bannerStroke, {Transparency = 0.3}, 0.6)
			task.wait(0.6)
		end
	end)

	local overlay = Instance.new("Frame")
	overlay.Size = UDim2.fromScale(1, 1)
	overlay.BackgroundColor3 = Color3.new(0, 0, 0)
	overlay.BackgroundTransparency = 1
	overlay.Parent = screen
	Utils.Tween(overlay, {BackgroundTransparency = 1}, 1)
	SetBlur(true)
	local main = Instance.new("Frame")
	main.Size = Configuration.Window.Size
	main.Position = UDim2.new(0.5, 0, 0.5, 60)
	main.AnchorPoint = Vector2.new(0.5, 0.5)
	main.BackgroundColor3 = Configuration.Colors.Bg
	main.BackgroundTransparency = 0.2
	main.ClipsDescendants = true
	main.Parent = screen
	Utils.Round(main, 24)
	Utils.Stroke(main, Color3.new(1, 1, 1), 1, 0.92)
	local glass = Instance.new("Frame")
	glass.Size = UDim2.fromScale(1, 1)
	glass.BackgroundColor3 = Color3.new(1, 1, 1)
	glass.BackgroundTransparency = 0.985
	glass.ZIndex = 0
	glass.Parent = main
	Utils.Round(glass, 24)
	local bar = Instance.new("Frame")
	bar.Size = UDim2.new(1, 0, 0, 54)
	bar.BackgroundTransparency = 1
	bar.Parent = main
	local dots = Instance.new("Frame")
	dots.Size = UDim2.new(0, 54, 0, 12)
	dots.Position = UDim2.new(0, 20, 0.5, 0)
	dots.AnchorPoint = Vector2.new(0, 0.5)
	dots.BackgroundTransparency = 1
	dots.Parent = bar
	local dColors = {
		Configuration.Colors.TrafficRed,
		Configuration.Colors.TrafficYellow,
		Configuration.Colors.TrafficGreen
	}
	for i, c in ipairs(dColors) do
		local d = Instance.new("Frame")
		d.Size = UDim2.fromOffset(12, 12)
		d.Position = UDim2.fromOffset((i - 1) * 18, 0)
		d.BackgroundColor3 = c
		d.BorderSizePixel = 0
		d.Parent = dots
		Utils.Round(d, 6)
	end
	local titleText = Instance.new("TextLabel")
	titleText.Size = UDim2.new(1, 0, 1, 0)
	titleText.Text = "JUNKIE"
	titleText.TextColor3 = Color3.new(1, 1, 1)
	titleText.TextTransparency = 0.7
	titleText.TextSize = 10
	titleText.Font = Enum.Font.GothamBold
	titleText.BackgroundTransparency = 1
	titleText.Parent = bar
	local content = Instance.new("ScrollingFrame")
	content.Size = UDim2.new(1, 0, 1, -54)
	content.Position = UDim2.new(0, 0, 0, 54)
	content.BackgroundTransparency = 1
	content.ScrollBarThickness = 0
	content.CanvasSize = UDim2.new(0, 0, 0, 440)
	content.Parent = main
	local list = Instance.new("UIListLayout")
	list.Padding = UDim.new(0, 24)
	list.HorizontalAlignment = Enum.HorizontalAlignment.Center
	list.Parent = content
	local pad = Instance.new("UIPadding")
	pad.PaddingTop = UDim.new(0, 5)
	pad.Parent = content
	local logoContainer = Instance.new("Frame")
	logoContainer.Size = UDim2.fromOffset(80, 80)
	logoContainer.BackgroundColor3 = Configuration.Colors.Primary
	logoContainer.Parent = content
	Utils.Round(logoContainer, 20)
	local grad = Instance.new("UIGradient")
	grad.Color = ColorSequence.new(Configuration.Colors.Primary, Configuration.Colors.PrimaryDark)
	grad.Rotation = 45
	grad.Parent = logoContainer
	local sIcon = Instance.new("ImageLabel")
	sIcon.Size = UDim2.fromScale(1, 1)
	sIcon.Position = UDim2.fromScale(0.5, 0.5)
	sIcon.AnchorPoint = Vector2.new(0.5, 0.5)
	sIcon.Image = Icons.JunkieNewIcon
	sIcon.ScaleType = Enum.ScaleType.Fit
	sIcon.BackgroundTransparency = 1
	sIcon.Parent = logoContainer
	local titleArea = Instance.new("Frame")
	titleArea.Size = UDim2.new(1, 0, 0, 44)
	titleArea.BackgroundTransparency = 1
	titleArea.Parent = content
	local mainTitle = Instance.new("TextLabel")
	mainTitle.Size = UDim2.new(1, 0, 0, 26)
	mainTitle.Text = "Junkie"
	mainTitle.TextColor3 = Color3.new(1, 1, 1)
	mainTitle.TextSize = 26
	mainTitle.Font = Enum.Font.GothamBold
	mainTitle.BackgroundTransparency = 1
	mainTitle.Parent = titleArea
	local subTitle = Instance.new("TextLabel")
	subTitle.Size = UDim2.new(1, 0, 0, 16)
	subTitle.Position = UDim2.fromOffset(0, 28)
	subTitle.Text = "junkie-development.de"
	subTitle.TextColor3 = Configuration.Colors.TextSec
	subTitle.TextSize = 13
	subTitle.Font = Enum.Font.Gotham
	subTitle.BackgroundTransparency = 1
	subTitle.Parent = titleArea
	local statusCard = Instance.new("Frame")
	statusCard.Size = UDim2.new(0, 280, 0, 68)
	statusCard.BackgroundColor3 = Color3.new(1, 1, 1)
	statusCard.BackgroundTransparency = 0.96
	statusCard.Parent = content
	Utils.Round(statusCard, 16)
	local sStroke = Utils.Stroke(statusCard, Color3.new(1, 1, 1), 1, 0.95)
	local sIconBg = Instance.new("Frame")
	sIconBg.Size = UDim2.fromOffset(42, 42)
	sIconBg.Position = UDim2.new(0, 14, 0.5, 0)
	sIconBg.AnchorPoint = Vector2.new(0, 0.5)
	sIconBg.BackgroundColor3 = Configuration.Colors.StatusIdle
	sIconBg.BackgroundTransparency = 0.9
	sIconBg.Parent = statusCard
	Utils.Round(sIconBg, 21)
	local sImg = Instance.new("ImageLabel")
	sImg.Size = UDim2.fromScale(0.5, 0.5)
	sImg.Position = UDim2.fromScale(0.5, 0.5)
	sImg.AnchorPoint = Vector2.new(0.5, 0.5)
	sImg.Image = Icons.Lock
	sImg.ImageColor3 = Configuration.Colors.StatusIdle
	sImg.BackgroundTransparency = 1
	sImg.Parent = sIconBg
	local sLabel = Instance.new("TextLabel")
	sLabel.Size = UDim2.new(1, -70, 0, 14)
	sLabel.Position = UDim2.fromOffset(70, 16)
	sLabel.Text = "CURRENT STATUS"
	sLabel.TextColor3 = Configuration.Colors.TextMuted
	sLabel.TextSize = 10
	sLabel.Font = Enum.Font.GothamBold
	sLabel.TextXAlignment = Enum.TextXAlignment.Left
	sLabel.BackgroundTransparency = 1
	sLabel.Parent = statusCard
	local sValue = Instance.new("TextLabel")
	sValue.Size = UDim2.new(1, -70, 0, 20)
	sValue.Position = UDim2.fromOffset(70, 32)
	sValue.Text = "No key detected"
	sValue.TextColor3 = Configuration.Colors.StatusIdle
	sValue.TextSize = 15
	sValue.Font = Enum.Font.GothamMedium
	sValue.TextXAlignment = Enum.TextXAlignment.Left
	sValue.BackgroundTransparency = 1
	sValue.Parent = statusCard
	local inputFrame = Instance.new("Frame")
	inputFrame.Size = UDim2.new(0, 280, 0, 52)
	inputFrame.BackgroundColor3 = Color3.new(1, 1, 1)
	inputFrame.BackgroundTransparency = 0.975
	inputFrame.Parent = content
	Utils.Round(inputFrame, 14)
	local iStroke = Utils.Stroke(inputFrame, Color3.new(1, 1, 1), 1, 0.95)
	local kIcon = Instance.new("ImageLabel")
	kIcon.Size = UDim2.fromOffset(18, 18)
	kIcon.Position = UDim2.new(0, 14, 0.5, 0)
	kIcon.AnchorPoint = Vector2.new(0, 0.5)
	kIcon.Image = Icons.Key
	kIcon.ImageColor3 = Configuration.Colors.TextMuted
	kIcon.BackgroundTransparency = 1
	kIcon.Parent = inputFrame
	local box = Instance.new("TextBox")
	box.Size = UDim2.new(1, -85, 1, 0)
	box.Position = UDim2.fromOffset(45, 0)
	box.Text = ""
	box.PlaceholderText = "Enter your key..."
	box.TextColor3 = Color3.new(1, 1, 1)
	box.TextSize = 14
	box.Font = Enum.Font.Gotham
	box.BackgroundTransparency = 1
	box.TextXAlignment = Enum.TextXAlignment.Left
	box.Parent = inputFrame
	local paste = Instance.new("ImageButton")
	paste.Size = UDim2.fromOffset(18, 18)
	paste.Position = UDim2.new(1, -14, 0.5, 0)
	paste.AnchorPoint = Vector2.new(1, 0.5)
	paste.Image = Icons.Copy
	paste.ImageColor3 = Configuration.Colors.TextMuted
	paste.BackgroundTransparency = 1
	paste.Parent = inputFrame
	local btnRow = Instance.new("Frame")
	btnRow.Size = UDim2.new(0, 280, 0, 50)
	btnRow.BackgroundTransparency = 1
	btnRow.Parent = content
	local redeem = Instance.new("TextButton")
	redeem.Size = UDim2.new(0.5, -8, 1, 0)
	redeem.BackgroundColor3 = Configuration.Colors.Primary
	redeem.Text = "Redeem"
	redeem.TextColor3 = Color3.new(1, 1, 1)
	redeem.Font = Enum.Font.GothamBold
	redeem.TextSize = 14
	redeem.AutoButtonColor = false
	redeem.Parent = btnRow
	Utils.Round(redeem, 14)
	local getKey = Instance.new("TextButton")
	getKey.Size = UDim2.new(0.5, -8, 1, 0)
	getKey.Position = UDim2.new(0.5, 8, 0, 0)
	getKey.BackgroundColor3 = Color3.new(1, 1, 1)
	getKey.BackgroundTransparency = 0.955
	getKey.Text = "Get Key"
	getKey.TextColor3 = Color3.new(1, 1, 1)
	getKey.Font = Enum.Font.GothamBold
	getKey.TextSize = 14
	getKey.AutoButtonColor = false
	getKey.Parent = btnRow
	Utils.Round(getKey, 14)
	Utils.Stroke(getKey, Color3.new(1, 1, 1), 1, 0.94)
	local function ApplyHover(btn)
		local baseColor = btn.BackgroundColor3
		btn.MouseEnter:Connect(
			function()
				Utils.Tween(
					btn,
					{
						BackgroundColor3 = baseColor:Lerp(Color3.new(1, 1, 1), 0.1)
					},
					0.2
				)
				Utils.Tween(
					btn,
					{
						Size = UDim2.new(btn.Size.X.Scale, btn.Size.X.Offset + 4, btn.Size.Y.Scale, btn.Size.Y.Offset + 2)
					},
					0.2
				)
			end
		)
		btn.MouseLeave:Connect(
			function()
				Utils.Tween(btn, {BackgroundColor3 = baseColor}, 0.2)
				Utils.Tween(
					btn,
					{
						Size = UDim2.new(btn.Size.X.Scale, btn.Size.X.Offset - 4, btn.Size.Y.Scale, btn.Size.Y.Offset - 2)
					},
					0.2
				)
			end
		)
	end
	ApplyHover(redeem)
	ApplyHover(getKey)
	box.Focused:Connect(
		function()
			Utils.Tween(iStroke, {Transparency = 0.5, Thickness = 1.2}, 0.3)
		end
	)
	box.FocusLost:Connect(
		function()
			Utils.Tween(iStroke, {Transparency = 0.95, Thickness = 1}, 0.3)
		end
	)
	local spinConnection
	local dotsThread
	local function SetStatus(state)
		if spinConnection then
			spinConnection:Disconnect()
			spinConnection = nil
			sImg.Rotation = 0
		end
		if dotsThread then
			task.cancel(dotsThread)
			dotsThread = nil
		end
		local color = Configuration.Colors.StatusIdle
		local icon = Icons.Lock
		local text = "No key detected"
		if state == "verifying" then
			color = Configuration.Colors.StatusVerifying
			icon = Icons.Loading
			text = "Verifying access"
			spinConnection =
				RunService.Heartbeat:Connect(
				function(dt)
					if not sImg or not sImg.Parent then
						if spinConnection then
							spinConnection:Disconnect()
						end
						spinConnection = nil
						return
					end
					sImg.Rotation = (sImg.Rotation + dt * 360) % 360
				end
			)
			local dots = {".", "..", "...", ""}
			local i = 1
			dotsThread =
				task.spawn(
				function()
					while sValue and sValue.Parent do
						if not sValue.Text:find("Verifying access", 1, true) then
							break
						end
						sValue.Text = text .. dots[i]
						i = (i % #dots) + 1
						task.wait(0.45)
					end
				end
			)
		elseif state == "success" then
			color = Configuration.Colors.StatusSuccess
			icon = Icons.CheckCircle
			text = "Access Granted"
		elseif state == "error" then
			color = Configuration.Colors.StatusError
			icon = Icons.XCircle
			text = "Invalid Key"
		end
		Utils.Tween(sValue, {TextColor3 = color}, 0.35)
		Utils.Tween(sImg, {ImageColor3 = color}, 0.35)
		Utils.Tween(sIconBg, {BackgroundColor3 = color}, 0.35)
		sValue.Text = text
		sImg.Image = icon
	end
	redeem.MouseButton1Click:Connect(
		function()
			local key = (box.Text:gsub("%s+", "")) -- trim spaces; keep case (work.ink tokens are lowercase)
			SetStatus("verifying")
			redeem.Text = "..."
			redeem.Active = false
            local result = Junkie.check_key(key)
			redeem.Active = true
			redeem.Text = "Redeem"
			if not result then
				SetStatus("error")
				ToastSystem.Create(screen, "API request failed: " .. tostring(result), "error")
				return
			end
			if result.valid then
                saveVerifiedKey(key)
                getgenv().SCRIPT_KEY = key
                SetStatus("success")
                ToastSystem.Create(screen, "Access granted!", "success", nil, status)
                task.wait(0.8)
                SetBlur(false)
                Utils.Tween(
                    main,
                    {
                        Position = UDim2.new(0.5, 0, 0.5, 100),
                        BackgroundTransparency = 1
                    },
                    0.7,
                    Enum.EasingStyle.Exponential,
                    Enum.EasingDirection.In
                )
                task.delay(
                    0.7,
                    function()
                        screen:Destroy()
                    end
                )
			else
				SetStatus("error")
				ToastSystem.Create(screen, result.message or "Invalid key", "error", nil, status)
			end
		end
	)
	getKey.MouseButton1Click:Connect(
		function()
			setclipboard(Junkie.get_key_link())
			ToastSystem.Create(screen, "Key link has been copied to clipboard", "success")
		end
	)
	paste.MouseButton1Click:Connect(
		function()
			ToastSystem.Create(screen, "Paste functionality not supported in Roblox (security reasons)", "warning")
		end
	)
	main.Position = UDim2.new(0.5, 0, 0.5, 100)
	main.BackgroundTransparency = 1
	Utils.Tween(
		main,
		{
			Position = UDim2.new(0.5, 0, 0.5, 0),
			BackgroundTransparency = 0.2
		},
		1,
		Enum.EasingStyle.Exponential
	)
	local dragging, dragStart, startPos
	bar.InputBegan:Connect(
		function(input)
			if input.UserInputType == Enum.UserInputType.MouseButton1 then
				dragging = true
				dragStart = input.Position
				startPos = main.Position
			end
		end
	)
	UserInputService.InputChanged:Connect(
		function(input)
			if dragging and input.UserInputType == Enum.UserInputType.MouseMovement then
				local delta = input.Position - dragStart
				main.Position =
					UDim2.new(startPos.X.Scale, startPos.X.Offset + delta.X, startPos.Y.Scale, startPos.Y.Offset + delta.Y)
			end
		end
	)
	UserInputService.InputEnded:Connect(
		function(input)
			if input.UserInputType == Enum.UserInputType.MouseButton1 then
				dragging = false
			end
		end
	)
	return screen
end

local savedKey = loadVerifiedKey()
local keyToCheck = savedKey
if not keyToCheck then
    keyToCheck = getgenv().SCRIPT_KEY
end

local result = Junkie.check_key(keyToCheck)
if result and result.valid then
    if result.message == "KEYLESS" then
        getgenv().SCRIPT_KEY = "KEYLESS"
    elseif result.message == "KEY_VALID" then
        if not savedKey and keyToCheck then
            saveVerifiedKey(keyToCheck)
        end
        getgenv().SCRIPT_KEY = keyToCheck
    else
        Build()
    end
else
    Build()
end

while not getgenv().SCRIPT_KEY do
    task.wait(0.1)
end
end
__y2k_keygate()
-- ===== Protected payload =====
-- Protected with Vm runtime. Tampering halts execution.
-- Vm protection runtime (bundled). Do not edit by hand.
local Crypt = (function()
--!nonstrict
-- ============================================================================
--  Crypt.lua  --  lightweight obfuscation / integrity primitives
--  Part of the Vm protection runtime. No external deps. Luau-safe.
--
--  Provides: XOR string cipher, FNV-1a hash, base64, and a small PRNG so the
--  runtime can hide embedded strings (URLs, function names) and verify
--  integrity without leaving plaintext secrets in the bytecode.
-- ============================================================================

local Crypt = {}

local schar, sbyte, ssub, srep = string.char, string.byte, string.sub, string.rep
local tconcat = table.concat
local bxor = bit32 and bit32.bxor or function(a, b)
	local r, p = 0, 1
	while a > 0 or b > 0 do
		local x, y = a % 2, b % 2
		if x ~= y then r = r + p end
		a, b, p = (a - x) / 2, (b - y) / 2, p * 2
	end
	return r
end

-- 32-bit multiply mod 2^32 that stays within double precision (2^53).
-- Splitting the accumulator into hi/lo 16-bit halves keeps every intermediate
-- product under 2^42, so no precision is lost (a plain h*16777619 overflows 2^53).
local function mul32(a, b)
	local ah = (a - a % 65536) / 65536   -- floor(a / 2^16), < 2^16
	local al = a % 65536                  -- a mod 2^16, < 2^16
	return ((ah * b % 65536) * 65536 + al * b) % 4294967296
end

-- FNV-1a 32-bit hash of a string (used for integrity fingerprints)
function Crypt.hash(s)
	local h = 2166136261
	for i = 1, #s do
		h = bxor(h, sbyte(s, i))
		h = mul32(h, 16777619)
	end
	return h
end

-- repeating-key XOR cipher (symmetric). key is a string.
function Crypt.xor(data, key)
	local out, kl = {}, #key
	for i = 1, #data do
		out[i] = schar(bxor(sbyte(data, i), sbyte(key, (i - 1) % kl + 1)))
	end
	return tconcat(out)
end

-- deterministic PRNG (xorshift) seeded from a string; for shuffling/jitter
function Crypt.rng(seed)
	local state = (type(seed) == "string") and Crypt.hash(seed) or (seed or 0x1234567)
	if state == 0 then state = 0x9E3779B9 end
	return function()
		state = bxor(state, (state * 32) % 4294967296)
		state = bxor(state, math.floor(state / 8))
		state = bxor(state, (state * 16384) % 4294967296)
		state = state % 4294967296
		return state / 4294967296
	end
end

-- base64 (so ciphertext survives as a string literal in the bundle)
local B64 = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
function Crypt.b64encode(data)
	local out = {}
	for i = 1, #data, 3 do
		local a, b, c = sbyte(data, i), sbyte(data, i + 1), sbyte(data, i + 2)
		local n = a * 65536 + (b or 0) * 256 + (c or 0)
		local c1 = math.floor(n / 262144) % 64
		local c2 = math.floor(n / 4096) % 64
		local c3 = math.floor(n / 64) % 64
		local c4 = n % 64
		out[#out + 1] = ssub(B64, c1 + 1, c1 + 1)
		out[#out + 1] = ssub(B64, c2 + 1, c2 + 1)
		out[#out + 1] = b and ssub(B64, c3 + 1, c3 + 1) or "="
		out[#out + 1] = c and ssub(B64, c4 + 1, c4 + 1) or "="
	end
	return tconcat(out)
end

local B64I
function Crypt.b64decode(data)
	if not B64I then
		B64I = {}
		for i = 1, #B64 do B64I[ssub(B64, i, i)] = i - 1 end
	end
	data = string.gsub(data, "[^" .. B64 .. "]", "")
	local out = {}
	for i = 1, #data, 4 do
		local a = B64I[ssub(data, i, i)] or 0
		local b = B64I[ssub(data, i + 1, i + 1)] or 0
		local c = B64I[ssub(data, i + 2, i + 2)]
		local d = B64I[ssub(data, i + 3, i + 3)]
		local n = a * 262144 + b * 4096 + (c or 0) * 64 + (d or 0)
		out[#out + 1] = schar(math.floor(n / 65536) % 256)
		if c then out[#out + 1] = schar(math.floor(n / 256) % 256) end
		if d then out[#out + 1] = schar(n % 256) end
	end
	return tconcat(out)
end

-- convenience: encrypt a plaintext to a portable token (b64(xor(data,key)))
function Crypt.seal(plaintext, key)
	return Crypt.b64encode(Crypt.xor(plaintext, key))
end
function Crypt.open(token, key)
	return Crypt.xor(Crypt.b64decode(token), key)
end

return Crypt

end)()
local Secure = (function()
--!nonstrict
-- ============================================================================
--  Secure.lua  --  capture real executor functions & expose protected proxies
--
--  THE CORE PROTECTION. At load time (before any spy can install hooks) we grab
--  references to the real executor functions into PRIVATE upvalues, then hand
--  the wrapped script only thin proxies. Because the proxies call the captured
--  originals directly, a spy that later hooks the GLOBAL `request` / `http` /
--  `readfile` never sees the script's calls -- they bypass the global.
--
--  Proxies are wrapped with newcclosure so they read as native C-closures:
--  iscclosure() passes, and getupvalues() is blocked on them by most executors,
--  hiding the captured originals from getgc/upvalue inspection.
-- ============================================================================

local Secure = {}

-- resolve the real global table as early as possible
local realG = (getgenv and getgenv()) or (getfenv and getfenv(0)) or _G
local rawget, rawset = rawget, rawset
local iscc = iscclosure
local newcc = newcclosure or function(f) return f end
local clonef = clonefunction or function(f) return f end

-- list of sensitive globals we proxy. (function-valued globals only)
local CAPTURE = {
	"request", "http_request", "readfile", "writefile", "appendfile", "isfile",
	"isfolder", "listfiles", "makefolder", "delfile", "delfolder", "loadstring",
	"getgenv", "getrawmetatable", "setrawmetatable", "hookfunction", "hookmetamethod",
	"newcclosure", "getnamecallmethod", "setclipboard", "queue_on_teleport",
	"getcustomasset", "fireclickdetector", "firetouchinterest", "fireproximityprompt",
	"isexecutorclosure", "checkcaller", "getconnections", "getcallingscript",
}

-- Capture the real functions. Returns a PRIVATE table (kept as an upvalue by the
-- caller -- never store this in a global).
function Secure.capture()
	local raw = {}

	-- http via the common executor spellings, in priority order
	raw.http = (syn and syn.request) or (http and http.request) or http_request or request
	-- guard: if http appears already hooked (became an l-closure), remember it
	raw.http_tampered = (iscc and raw.http and not iscc(raw.http)) or false

	for _, name in ipairs(CAPTURE) do
		local fn = rawget(realG, name)
		if type(fn) == "function" then
			-- clone where supported so even a later identity-swap of the global
			-- can't reach our reference
			local ok, c = pcall(clonef, fn)
			raw[name] = ok and c or fn
			raw[name .. "_genuine"] = (iscc and iscc(fn)) or false
		end
	end

	-- HttpGet/HttpGetAsync live on `game`; capture bound callers
	local okGame = pcall(function() return game and game.HttpGet end)
	if okGame and game then
		raw.HttpGet = function(url, ...) return game:HttpGet(url, ...) end
		raw.HttpGetAsync = function(url, ...) return game:HttpGetAsync(url, ...) end
	end

	return raw
end

-- Build the proxy table the sandbox exposes. `raw` is the private capture.
-- Each proxy is a newcclosure so its upvalues (the real fn) are not inspectable.
function Secure.proxies(raw)
	local P = {}

	local function wrap(realFn)
		if type(realFn) ~= "function" then return nil end
		return newcc(function(...) return realFn(...) end)
	end

	-- generic passthrough proxies
	for _, name in ipairs(CAPTURE) do
		if raw[name] then P[name] = wrap(raw[name]) end
	end

	-- unified HTTP proxy (the prime spy target). Accepts the standard {Url=...}.
	if raw.http then
		local http = raw.http
		P.request = newcc(function(opts) return http(opts) end)
		P.http_request = P.request
		if syn then P.syn = { request = P.request } end
	end
	if raw.HttpGet then
		P.HttpGet = newcc(function(url, ...) return raw.HttpGet(url, ...) end)
		P.HttpGetAsync = newcc(function(url, ...) return raw.HttpGetAsync(url, ...) end)
	end

	return P
end

-- Snapshot identities so Integrity can detect later replacement of our proxies.
function Secure.fingerprint(P)
	local fp = {}
	for k, v in pairs(P) do
		if type(v) == "function" then fp[k] = v end
	end
	return fp
end

return Secure

end)()
local Environment = (function()
--!nonstrict
-- ============================================================================
--  Environment.lua  --  the sealed sandbox the wrapped script runs inside
--
--  Builds a custom _ENV whose:
--    * function-valued executor globals resolve to PROTECTED PROXIES
--    * everything else falls through to the real globals (so game, workspace,
--      Instance, math, string, task, etc. all work -- full Luau semantics)
--    * writes stay local to the sandbox (script can't pollute real _G)
--    * the metatable is private (Integrity verifies it wasn't swapped)
--
--  This is the isolation layer: the script believes it has a normal global
--  environment, but its sensitive calls are routed through the Vm.
-- ============================================================================

local Environment = {}

function Environment.build(proxies, realG)
	realG = realG or (getgenv and getgenv()) or _G

	-- the sandbox's own storage for globals the script defines
	local store = {}

	-- private metatable (kept out of the sandbox; Integrity holds a ref)
	local mt = {}

	mt.__index = function(_, key)
		-- 1. protected proxy?
		local p = proxies[key]
		if p ~= nil then return p end
		-- 2. script-local global?
		local s = store[key]
		if s ~= nil then return s end
		-- 3. fall through to the real environment
		return realG[key]
	end

	mt.__newindex = function(_, key, value)
		-- keep all writes inside the sandbox (never touch real globals)
		store[key] = value
	end

	-- unique private lock token. __metatable makes getmetatable(env) return THIS
	-- (hiding the real mt) and makes setmetatable(env, ...) error -- so the env's
	-- metatable cannot be swapped. Integrity verifies this token is still in place.
	local lock = {}
	mt.__metatable = lock

	local env = setmetatable({}, mt)

	-- expose a sandboxed getfenv/getgenv so the script's own introspection
	-- returns the sandbox, not the real globals (don't leak the boundary)
	store.getgenv = function() return env end
	store._G = env
	store.shared = store.shared or {}

	return env, mt, store, lock
end

return Environment

end)()
local Integrity = (function()
--!nonstrict
-- ============================================================================
--  Integrity.lua  --  anti-tamper / anti-penetration
--
--  Verifies the runtime hasn't been hooked or swapped, both at startup and via
--  a background watchdog. On tamper it triggers a caller-supplied onTamper
--  (the Vm wipes the sandbox + halts).
--
--  Checks:
--   * capture genuineness   -- were the executor funcs already hooked at capture?
--   * proxy identity         -- have our proxies been replaced since fingerprint?
--   * env seal               -- is the sandbox __index/__newindex intact?
--   * hostile introspection  -- is something actively decompiling/hooking us?
--   * source checksum        -- does the protected payload still match?
-- ============================================================================

local Integrity = {}

local iscc = iscclosure
local getus = getupvalues or (debug and debug.getupvalues)

-- 1. Were any captured executor functions already hooks (l-closures) at capture?
function Integrity.checkCapture(raw)
	local suspicious = {}
	if raw.http_tampered then suspicious[#suspicious + 1] = "http" end
	for k, v in pairs(raw) do
		if string.sub(k, -8) == "_genuine" and v == false then
			suspicious[#suspicious + 1] = string.sub(k, 1, -9)
		end
	end
	return suspicious
end

-- 2. Our proxies must still be the exact functions we created.
function Integrity.checkProxies(P, fingerprint)
	for k, original in pairs(fingerprint) do
		if P[k] ~= original then return false, k end
	end
	return true
end

-- 3. The sandbox env metatable must be intact (not re-pointed to leak globals).
function Integrity.checkEnv(env, expectedMT)
	local mt = getmetatable(env)
	if mt ~= expectedMT then return false, "metatable" end
	return true
end

-- 4. Best-effort: detect if our own proxies have become inspectable (a sign a
--    de-hook tool unwrapped the cclosure). On a healthy executor getupvalues on
--    a newcclosure should be empty/blocked; non-empty => someone unwrapped it.
function Integrity.checkOpaque(P)
	if not getus then return true end
	for _, v in pairs(P) do
		if type(v) == "function" then
			local ok, ups = pcall(getus, v)
			if ok and type(ups) == "table" and next(ups) ~= nil then
				return false
			end
		end
	end
	return true
end

-- run all startup checks; returns ok, reason
function Integrity.startup(ctx)
	local sus = Integrity.checkCapture(ctx.raw)
	if #sus > 0 and ctx.strict then
		return false, "capture-hooked:" .. table.concat(sus, ",")
	end
	local okP, badKey = Integrity.checkProxies(ctx.proxies, ctx.fingerprint)
	if not okP then return false, "proxy-swapped:" .. tostring(badKey) end
	local okE, why = Integrity.checkEnv(ctx.env, ctx.envLock)
	if not okE then return false, "env-" .. tostring(why) end
	if not Integrity.checkOpaque(ctx.proxies) then return false, "opaque-broken" end
	return true
end

-- background watchdog: re-run cheap checks on an interval and self-destruct.
-- Spawns through the Memory scope (ctx.mem) so the thread is tracked and
-- cancelled on cleanup -- it can never leak past the script's lifetime.
function Integrity.watchdog(ctx, onTamper)
	local wait_ = (task and task.wait) or wait
	local body = function()
		while ctx.alive do
			wait_(ctx.interval or 2)
			if not ctx.alive then return end
			local okP, badKey = Integrity.checkProxies(ctx.proxies, ctx.fingerprint)
			local okE = Integrity.checkEnv(ctx.env, ctx.envLock)
			if not okP or not okE then
				ctx.alive = false
				pcall(onTamper, okP and "env" or ("proxy:" .. tostring(badKey)))
				return
			end
		end
	end
	if ctx.mem and ctx.mem.spawn then
		ctx.mem:spawn(body)
	else
		local spawn = (task and task.spawn) or spawn
		if spawn then spawn(body) end
	end
end

return Integrity

end)()
local Stealth = (function()
--!nonstrict
-- ============================================================================
--  Stealth.lua  --  comprehensive environment spoofing / anti-detection
--
--  Covers the full sUNC executor surface (docs.sunc.su). For each function an
--  anti-cheat could use to fingerprint the executor, detect hooks, or scan for
--  injected objects, we install a fake that answers "clean" -- while leaving the
--  function usable for everyone else.
--
--  Technique: hookfunction (rewrites the function OBJECT, so even a reference
--  the AC captured early is affected), replacement wrapped in newcclosure (stays
--  a C-closure -> passes iscclosure). Everything pcall-guarded; only spoofs what
--  the executor actually exposes.
--
--  HONEST: beats ACs that read these globals at runtime and trust them. Does NOT
--  beat an AC that ran fully before you, re-implements checks in its own VM, or
--  validates server-side. Raises the bar across games.
-- ============================================================================

local Stealth = {}

local realG = (getgenv and getgenv()) or (getfenv and getfenv(0)) or _G
local newcc = newcclosure or function(f) return f end
local clonef = clonefunction
local hookf = hookfunction
local cloneref_ = cloneref or function(x) return x end
local rawget, rawset = rawget, rawset

-- private registries (weak so we never pin objects alive)
local hiddenObjs = setmetatable({}, { __mode = "k" })  -- hide from gc/instance scans
local genuineFns = setmetatable({}, { __mode = "k" })  -- report as un-hooked / ours
local ourScripts = setmetatable({}, { __mode = "k" })  -- hide script bytecode/closure
local installed  = false

function Stealth.hide(o)        if o ~= nil then hiddenObjs[o] = true end return o end
function Stealth.markGenuine(f) if type(f) == "function" then genuineFns[f] = true end return f end
function Stealth.hideScript(s)  if s ~= nil then ourScripts[s] = true end return s end

-- ---- hook helpers ---------------------------------------------------------
-- CRITICAL: after hookfunction(real, repl), the `real` OBJECT behaves like repl.
-- So the replacement must NOT call `real` on its passthrough path (that would be
-- infinite recursion -> C stack overflow). We clone the original FIRST and have
-- the replacement call the unhooked clone. If we can't clone, we fall back to a
-- plain global swap (which leaves `real` itself untouched, so calling it is safe).
local function emplace(container, name, build)
	if type(container) ~= "table" then return end
	local real = rawget(container, name)
	if type(real) ~= "function" then return end
	if hookf and clonef then
		local okc, orig = pcall(clonef, real)
		if okc and type(orig) == "function" then
			local repl = newcc(build(orig))         -- repl -> clone (unhooked): safe
			genuineFns[repl] = true; hiddenObjs[repl] = true
			if pcall(hookf, real, repl) then return end
		end
	end
	-- fallback: global/table swap, repl -> real (real is NOT hooked here): safe
	local repl = newcc(build(real))
	genuineFns[repl] = true; hiddenObjs[repl] = true
	pcall(rawset, container, name, repl)
end

local function spoof(name, build)            emplace(realG, name, build) end
local function spoofIn(tbl, name, build)     emplace(tbl, name, build) end

-- filter our hidden/genuine objects out of an array-like result table.
local function filterArray(t)
	if type(t) ~= "table" then return t end
	local out = {}
	for i = 1, #t do
		local v = t[i]
		if not (hiddenObjs[v] or genuineFns[v]) then out[#out + 1] = v end
	end
	return out
end

-- ===========================================================================
function Stealth.install(opts)
	if installed then return end
	installed = true
	opts = opts or {}
	local fakeName = opts.spoofName            -- nil => "no executor"
	local fakeVer  = opts.spoofVersion or "1.0.0"

	-- DISGUISE: a real game LocalScript (cloneref'd) to report as the "calling
	-- script", so introspection sees a legit script instead of getcallingscript()
	-- == nil (which screams "injected"). On by default; opts.disguise=false to skip.
	local decoyScript = nil
	if opts.disguise ~= false then
		pcall(function()
			local lp = game:GetService("Players").LocalPlayer
			local char = lp and lp.Character
			decoyScript = (char and char:FindFirstChild("Animate"))
				or (lp and lp:FindFirstChildWhichIsA("LocalScript", true))
		end)
		if decoyScript then pcall(function() decoyScript = cloneref_(decoyScript) end) end
	end

	-- 1) IDENTITY ----------------------------------------------------------
	for _, n in ipairs({ "identifyexecutor", "getexecutorname", "iexecutor" }) do
		spoof(n, function() return function()
			if fakeName then return fakeName, fakeVer end
			return nil
		end end)
	end

	-- 2) CLOSURE CHECKS ----------------------------------------------------
	spoof("iscclosure",       function(r) return function(f) if genuineFns[f] then return true  end return r(f) end end)
	spoof("isexecutorclosure",function(r) return function(f) if genuineFns[f] then return false end return r(f) end end)
	spoof("isourclosure",     function(r) return function(f) if genuineFns[f] then return false end return r(f) end end)
	spoof("islclosure",       function(r) return function(f) if genuineFns[f] then return false end return r(f) end end)
	spoof("checkcaller",      function(r) return function() return false end end)
	-- stable fake hash for our funcs so repeated checks stay consistent
	spoof("getfunctionhash",  function(r) return function(f) if genuineFns[f] then return "00000000000000000000000000000000" end return r(f) end end)

	-- 3) ENVIRONMENT / GC scans -- strip our objects ----------------------
	spoof("getgc",     function(r) return function(...) return filterArray(r(...)) end end)
	spoof("filtergc",  function(r) return function(...) local t = r(...) return type(t)=="table" and filterArray(t) or t end end)
	spoof("getreg",    function(r) return function(...) return filterArray(r(...)) end end)
	-- getgenv/getrenv must keep identity (callers rely on it); objects already hidden via getgc

	-- 4) INSTANCE scans -- strip our injected instances -------------------
	spoof("getinstances",    function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getnilinstances", function(r) return function(...) return filterArray(r(...)) end end)

	-- 5) SCRIPT scans -- hide our scripts/closures ------------------------
	spoof("getloadedmodules", function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getrunningscripts",function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getscripts",       function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getcallingscript", function(r) return function(...) local s = r(...); if ourScripts[s] or s == nil then return decoyScript end return s end end)
	spoof("getscriptbytecode",function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	spoof("getscriptclosure", function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	spoof("getscripthash",    function(r) return function(s, ...) if ourScripts[s] then return "" end return r(s, ...) end end)
	spoof("getsenv",          function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)

	-- 6) DEBUG introspection -- blank out for OUR functions ---------------
	if debug then
		spoofIn(debug, "getupvalue",  function(r) return function(f, ...) if genuineFns[f] then return nil end return r(f, ...) end end)
		spoofIn(debug, "getupvalues", function(r) return function(f, ...) if genuineFns[f] then return {}  end return r(f, ...) end end)
		spoofIn(debug, "getconstant", function(r) return function(f, ...) if genuineFns[f] then return nil end return r(f, ...) end end)
		spoofIn(debug, "getconstants",function(r) return function(f, ...) if genuineFns[f] then return {}  end return r(f, ...) end end)
		spoofIn(debug, "getproto",    function(r) return function(f, ...) if genuineFns[f] then return nil end return r(f, ...) end end)
		spoofIn(debug, "getprotos",   function(r) return function(f, ...) if genuineFns[f] then return {}  end return r(f, ...) end end)
	end
	-- top-level mirrors (some executors expose these globally too)
	for _, n in ipairs({ "getupvalue","getupvalues","getconstant","getconstants","getproto","getprotos" }) do
		spoof(n, function(r) return function(f, ...)
			if genuineFns[f] then
				if string.sub(n, -1) == "s" then return {} end
				return nil
			end
			return r(f, ...)
		end end)
	end

	-- 7) common executor extras (Volt/Synapse/etc. spellings that may exist) ----
	for _, n in ipairs({ "getexecutorname", "getexecutor", "getexecutorinfo" }) do
		spoof(n, function() return function()
			if fakeName then return fakeName, fakeVer end
			return nil
		end end)
	end
	-- decompiler-style probes: refuse on our scripts
	for _, n in ipairs({ "decompile", "disassemble", "dumpstring" }) do
		spoof(n, function(r) return function(s, ...) if ourScripts[s] then return "" end return r(s, ...) end end)
	end

	-- 7b) Potassium / extended closure + thread + hook checks --------------
	-- the big one: isfunctionhooked must say NO for the funcs your cheat hooks
	spoof("isfunctionhooked", function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	spoof("isnewcclosure",    function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	spoof("isourclosure",     function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	-- "is this the executor / a hook thread" -> no
	spoof("isourthread",      function(r) return function() return false end end)
	-- thread/script linkage: don't reveal our scripts
	spoof("getscriptfromthread", function(r) return function(t, ...) local s = r(t, ...) if ourScripts[s] then return nil end return s end end)
	spoof("getscriptthread",     function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	spoof("gettenv",             function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)

	-- Potassium oth.* (original-thread hooking) table
	local oth = rawget(realG, "oth")
	if type(oth) == "table" then
		spoofIn(oth, "is_hook_thread", function(r) return function() return false end end)
	end

	-- debug.* extras present on Potassium
	if debug then
		spoofIn(debug, "getcallstack", function(r) return function(...) return r(...) end end)  -- seam: frames aren't our objects
		-- getregistry: return a filtered COPY with our objects removed (AC scans are read-only)
		spoofIn(debug, "getregistry", function(r) return function(...)
			local reg = r(...)
			if type(reg) ~= "table" then return reg end
			local out = {}
			for k, v in pairs(reg) do
				if not (hiddenObjs[k] or hiddenObjs[v] or genuineFns[k] or genuineFns[v]) then
					out[k] = v
				end
			end
			return out
		end end)
		spoofIn(debug, "getinfo", function(r) return function(...) return r(...) end end)  -- seam
	end

	-- metatable seams: only safe to touch CONDITIONALLY. We do NOT blanket-fake
	-- getrawmetatable/getnamecallmethod -- faking the real game metatable breaks
	-- everything. If YOUR cheat hooks __namecall, register the clean function via
	-- Stealth.markGenuine(yourHook) and add a targeted getrawmetatable spoof.

	-- 8) USER-SUPPLIED EXTENSIONS (add Volt-specific names without editing code) -
	--    opts.identity   = { "voltname", ... }     -> spoofed like identifyexecutor
	--    opts.gcFilters  = { "somelist", ... }     -> array results have our objs removed
	--    opts.genuine    = { "iscustom", ... }     -> return clean for our funcs
	--    opts.scriptHide = { "getbytecode2", ... } -> return nothing for our scripts
	for _, n in ipairs(opts.identity or {}) do
		spoof(n, function() return function() if fakeName then return fakeName, fakeVer end return nil end end)
	end
	for _, n in ipairs(opts.gcFilters or {}) do
		spoof(n, function(r) return function(...) local t = r(...) return type(t)=="table" and filterArray(t) or t end end)
	end
	for _, n in ipairs(opts.genuine or {}) do
		spoof(n, function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	end
	for _, n in ipairs(opts.scriptHide or {}) do
		spoof(n, function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	end

	return true
end

return Stealth

end)()
local Memory = (function()
--!nonstrict
-- ============================================================================
--  Memory.lua  --  resource scope + leak/overflow protection
--
--  Every thread, connection and disposable the VM creates is registered in a
--  scope. When the script ends (return, error, or tamper) the scope is torn down
--  deterministically: threads cancelled, connections disconnected, tables
--  cleared, GC forced. Plus a budget guard that collects GC the moment memory
--  crosses a threshold, so a runaway/hostile script can't balloon the VM.
--
--  Design notes:
--   * Registries that hold game objects use WEAK keys so they never pin memory.
--   * The scope holds STRONG refs to threads/connections (so it can cancel them)
--     but cleanup is GUARANTEED to run, bounding their lifetime.
--   * Counters are capped; nothing grows unbounded.
-- ============================================================================

local Memory = {}
Memory.__index = Memory

local taskLib   = task
local taskSpawn = (taskLib and taskLib.spawn) or spawn
local taskWait  = (taskLib and taskLib.wait) or wait
local taskDefer = (taskLib and taskLib.defer) or taskSpawn
local taskCancel = taskLib and taskLib.cancel
local cg = collectgarbage

local MAX_TRACKED = 4096   -- hard cap so the bookkeeping itself can't leak

function Memory.new()
	return setmetatable({
		alive = true,
		threads = {},
		conns = {},
		disposers = {},
		count = 0,
	}, Memory)
end

local function bounded(self)
	return self.count < MAX_TRACKED
end

-- spawn a tracked thread (auto-cancelled on cleanup)
function Memory:spawn(fn)
	if not self.alive or not bounded(self) then return end
	local co = taskSpawn(fn)
	self.threads[#self.threads + 1] = co
	self.count = self.count + 1
	return co
end

-- track an arbitrary resource with a disposer
function Memory:track(obj, dispose)
	if not self.alive or not bounded(self) then return obj end
	if dispose then
		self.disposers[#self.disposers + 1] = dispose
		self.count = self.count + 1
	end
	return obj
end

-- track a signal connection (auto-disconnected on cleanup)
function Memory:connect(signal, fn)
	if not self.alive or not bounded(self) then return end
	local ok, c = pcall(function() return signal:Connect(fn) end)
	if ok and c then
		self.conns[#self.conns + 1] = c
		self.count = self.count + 1
		return c
	end
end

-- deterministic teardown -- safe to call multiple times
function Memory:cleanup()
	if not self.alive then return end
	self.alive = false
	for _, c in ipairs(self.conns) do
		pcall(function() if c.Disconnect then c:Disconnect() elseif c.disconnect then c:disconnect() end end)
	end
	if taskCancel then
		for _, co in ipairs(self.threads) do pcall(taskCancel, co) end
	end
	for _, d in ipairs(self.disposers) do pcall(d) end
	self.conns, self.threads, self.disposers, self.count = {}, {}, {}, 0
	if cg then pcall(cg, "collect") end
end

-- memory-budget guard: force GC when usage crosses the threshold; if it stays
-- over after a collect, escalate to onOverflow (the Vm halts).
function Memory:guard(opts)
	opts = opts or {}
	local budgetKB = opts.budgetKB or 700000   -- ~700 MB ceiling by default
	local interval = opts.interval or 4
	self:spawn(function()
		while self.alive do
			taskWait(interval)
			if not self.alive then return end
			local used = cg and cg("count") or 0     -- KB
			if used > budgetKB then
				if cg then pcall(cg, "collect") end
				used = cg and cg("count") or 0
				if used > budgetKB and opts.onOverflow then
					pcall(opts.onOverflow, used)
					return
				end
			end
		end
	end)
end

return Memory

end)()
local Defense = (function()
--!nonstrict
-- ============================================================================
--  Defense.lua  --  detect tools SPYING on your script (anti-tamper)
--
--  These detect OTHER exploiters' inspection tools so your script can react
--  (halt / hide) before its logic or remotes are stolen:
--    * HTTP spy      -- request/http hooked (closure-type check vs captured original)
--    * namecall hook -- __namecall identity changed (IY-style stack inspection)
--    * remote spy    -- gcinfo spike on FireServer (spies deep-clone args)  [opt-in]
--    * Dex explorer  -- weak-table service-cache persistence                [opt-in]
--
--  IMPORTANT: this is ANTI-SPY (protect your code from other exploiters), NOT
--  anti-cheat. It does nothing against the GAME's AC -- and the remote/dex probes
--  even ADD client AC surface (they fire a remote / force GC). Keep those opt-in.
-- ============================================================================

local Defense = {}

local gcinfo_   = gcinfo or function() return (collectgarbage and collectgarbage("count")) or 0 end
local cloneref_ = cloneref or function(x) return x end
local collect   = collectgarbage
local iscc      = iscclosure       -- captured at load; Stealth passes through for non-ours
local dbinfo    = debug and debug.info

-- 1) HTTP spy: a spy hooks the global request -> it becomes an l-closure -------
-- get the real __namecall fn via an errored game:IsA() ----------------------
local function actualNamecall()
	local nc, caller
	if not dbinfo then return nil end
	xpcall(function() return game:IsA() end, function()
		nc, caller = dbinfo(2, "f"), dbinfo(3, "f")
	end)
	return nc, caller
end

local function remoteSpike()
	local ok, spike = pcall(function()
		local re = Instance.new("RemoteEvent")
		local payload = { 1, 2, 3, { nested = true }, "probe" }
		local before = gcinfo_()
		pcall(function() re:FireServer(payload) end)
		local after = gcinfo_()
		pcall(function() re:Destroy() end)
		return after - before
	end)
	return (ok and type(spike) == "number") and spike or 0
end

-- BASELINE: snapshot the environment AFTER your script has set up its own hooks,
-- so YOUR hooks are treated as "normal". Only CHANGES after this (a spy) trigger.
-- Until baseline() is called, the change-detectors stay silent (no false positives).
Defense._snap = nil
function Defense.baseline()
	local realG = (getgenv and getgenv()) or _G
	Defense._snap = {
		ready = true,
		nc = (actualNamecall()),
		request = rawget(realG, "request"),
		http_request = rawget(realG, "http_request"),
		getgc = rawget(realG, "getgc"),     -- a dumper re-hooking getgc -> identity change
		spike = remoteSpike(),
	}
	return true
end

-- getgc-scan: someone re-hooked getgc (a memory scanner/dumper) after baseline
function Defense.detectGetgcHook()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local realG = (getgenv and getgenv()) or _G
	local cur = rawget(realG, "getgc")
	if cur and s.getgc and cur ~= s.getgc then return true, "getgc re-hooked (memory scan)" end
	return false
end

-- spy-tool GLOBALS (Hydroxide/SimpleSpy/etc. set flags or tables in getgenv)
local SPY_GLOBALS = { "Hydroxide", "oh_load", "SimpleSpy", "SimpleSpyExecuted", "RemoteSpyV3", "IY_LOADED" }
function Defense.detectSpyGlobals()
	local ok, g = pcall(getgenv)
	if ok and type(g) == "table" then
		for _, n in ipairs(SPY_GLOBALS) do
			if rawget(g, n) ~= nil then return true, "global " .. n end
		end
	end
	return false
end

-- 1) HTTP spy: the request function IDENTITY changed since baseline (newly hooked)
function Defense.detectHttpSpy()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local realG = (getgenv and getgenv()) or _G
	for _, n in ipairs({ "request", "http_request" }) do
		local cur = rawget(realG, n)
		if cur and s[n] and cur ~= s[n] then return true, n .. " changed after baseline" end
	end
	return false
end

-- 2) namecall hook: __namecall identity changed since baseline
function Defense.detectNamecallHook()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local nc = actualNamecall()
	if s.nc and nc and nc ~= s.nc then return true, "__namecall changed after baseline" end
	return false
end

-- 3) remote spy: gc spike on FireServer rose ABOVE the baseline (a new arg-cloner)
function Defense.detectRemoteSpy()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local spike = remoteSpike()
	if spike > (s.spike or 0) + 64 then
		return true, "FireServer gc spike " .. tostring(spike)
	end
	return false
end

-- 4a) Infinite Yield (and similar admin tools) set a known global flag --------
function Defense.detectInfiniteYield()
	local ok, g = pcall(getgenv)
	if ok and type(g) == "table" then
		if rawget(g, "IY_LOADED") == true then return true, "Infinite Yield" end
	end
	return false
end

-- 4b) Spy/explorer GUIs (Dex, RemoteSpy, SimpleSpy, Hydroxide, IY window) ------
-- scans CoreGui, the executor-hidden gui (gethui), and PlayerGui by exact name.
-- PRECISE name matching: exact known names, plus controlled version patterns,
-- so we don't false-positive on legit GUIs (e.g. "Dexterity" must NOT match "dex").
local EXACT = {
	["dex"] = true, ["dex explorer"] = true, ["remotespy"] = true, ["remote spy"] = true,
	["simplespy"] = true, ["simple spy"] = true, ["hydroxide"] = true,
}
local function isSpyName(nm)
	if EXACT[nm] then return true end
	if string.match(nm, "^dex%s*v?%d") then return true end          -- "dex v4", "dex 5"
	if string.match(nm, "^remotespy") then return true end
	if string.match(nm, "^simplespy") then return true end
	if string.match(nm, "^hydroxide") then return true end
	return false
end
function Defense.detectSpyGui()
	local parents = {}
	pcall(function() parents[#parents + 1] = game:GetService("CoreGui") end)
	if gethui then pcall(function() parents[#parents + 1] = gethui() end) end
	pcall(function()
		local pg = game:GetService("Players").LocalPlayer:FindFirstChild("PlayerGui")
		if pg then parents[#parents + 1] = pg end
	end)
	for _, p in ipairs(parents) do
		local ok, kids = pcall(function() return p:GetChildren() end)
		if ok then
			for _, c in ipairs(kids) do
				if isSpyName(string.lower(c.Name)) then return true, "GUI: " .. c.Name end
			end
		end
	end
	return false
end

-- 4) Dex: it strong-caches services, so a weak ref survives a forced GC -------
function Defense.detectDex()
	local ok, persisted = pcall(function()
		local weak = setmetatable({}, { __mode = "v" })
		weak[1] = cloneref_(game:GetService("TestService"))
		weak[1] = weak[1]   -- (kept only in the weak table after this scope)
		if collect then for _ = 1, 3 do pcall(collect, "collect") end end
		return weak[1] ~= nil
	end)
	return ok and persisted == true
end

-- SaveInstance guard: hook saveinstance-family so a game/script DUMP is caught
-- the moment it's attempted. Call once (from the watchdog) with the reaction.
function Defense.installSaveGuard(onDetect)
	local realG = (getgenv and getgenv()) or _G
	local newcc_ = newcclosure or function(f) return f end
	local hookf, clonef = hookfunction, clonefunction
	for _, n in ipairs({ "saveinstance", "synsaveinstance", "SaveInstance", "saveplace" }) do
		local f = rawget(realG, n)
		if type(f) == "function" and hookf and clonef then
			local ok, orig = pcall(clonef, f)
			if ok then
				pcall(hookf, f, newcc_(function(...)
					pcall(onDetect, "saveinstance", n)
					return orig(...)
				end))
			end
		end
	end
end

-- run a scan; returns array of { name = , detail = }
function Defense.scan(opts)
	opts = opts or {}
	local found = {}
	local function run(enabled, fn, name, arg)
		if not enabled then return end
		local ok, detail = fn(arg)
		if ok then found[#found + 1] = { name = name, detail = detail or "" } end
	end
	run(opts.iy ~= false,        Defense.detectInfiniteYield, "infinite-yield")
	run(opts.gui ~= false,       Defense.detectSpyGui,        "spy-gui")     -- Dex/RemoteSpy/IY window
	run(opts.globals ~= false,   Defense.detectSpyGlobals,    "spy-global")  -- Hydroxide/SimpleSpy/etc.
	run(opts.http ~= false,      Defense.detectHttpSpy,       "http-spy")
	run(opts.namecall ~= false,  Defense.detectNamecallHook,  "namecall-hook")
	run(opts.getgc ~= false,     Defense.detectGetgcHook,     "getgc-scan")  -- dumper re-hooked getgc
	run(opts.remote == true,     Defense.detectRemoteSpy,     "remote-spy")  -- opt-in (fires a remote)
	run(opts.dex == true,        Defense.detectDex,           "dex")         -- opt-in (forces GC)
	return found
end

-- watchdog: scan promptly then on an interval; call onDetect on first hit.
-- Light probes (IY/GUI/http/namecall) run every tick; HEAVY probes (remote gc
-- spike, Dex weak-table) run only every Nth tick so they don't spam remote-fires
-- or force GC constantly. Heavy probes are ON unless explicitly set to false.
function Defense.watchdog(ctx, onDetect, opts)
	opts = opts or {}
	-- proactive SaveInstance dump guard (fires the moment a dump is attempted)
	pcall(Defense.installSaveGuard, onDetect)
	local body = function()
		local wait_ = (task and task.wait) or wait
		wait_(opts.startDelay or 1)            -- let tools finish loading
		-- reliable signals (IY global, Dex/spy GUI by name, http hook, namecall hook)
		-- react on the FIRST hit. Only the noisy probes need a 2nd confirmation.
		local NOISY = { ["remote-spy"] = true, ["dex"] = true }
		local n, lastHit, confirm = 0, nil, 0
		-- baseline after a grace period so the script's OWN hooks aren't flagged
		-- (Vm also baselines right after the main chunk; whichever fires first wins).
		local graceUntil = (tick and tick() or 0) + (opts.gracePeriod or 4)
		while ctx.alive do
			n = n + 1
			if not (Defense._snap and Defense._snap.ready) and (tick and tick() or 0) >= graceUntil then
				pcall(Defense.baseline)
			end
			local heavy = (n % (opts.heavyEvery or 5)) == 0
			local hits = Defense.scan({
				iy = opts.iy, gui = opts.gui, globals = opts.globals,
				http = opts.http, namecall = opts.namecall, getgc = opts.getgc,
				remote = (opts.remote ~= false) and heavy,   -- throttled, on by default
				dex = (opts.dex ~= false) and heavy,           -- throttled, on by default
				raw = ctx.raw,
			})
			if #hits > 0 then
				local h = hits[1]
				local need = NOISY[h.name] and 2 or 1        -- reliable = instant, noisy = confirm twice
				if h.name == lastHit then confirm = confirm + 1
				else lastHit, confirm = h.name, 1 end
				if confirm >= need then
					pcall(onDetect, h.name, h.detail)
					return
				end
			else
				lastHit, confirm = nil, 0
			end
			wait_(opts.interval or 3)
		end
	end
	if ctx.mem and ctx.mem.spawn then ctx.mem:spawn(body)
	else local s = (task and task.spawn) or spawn if s then s(body) end end
end

return Defense

end)()
local Neuter = (function()
--!nonstrict
-- ============================================================================
--  Neuter.lua  --  best-effort anti-cheat neutralizer (with honest reporting)
--
--  Attempts, in order, every CLIENT-SIDE technique to blind an AC, and REPORTS
--  the outcome of each. If it can't bypass, it says so loudly:
--      "AC bypass fail (error; <reason>)"
--  rather than silently pretending you're undetected.
--
--  Strategies:
--    1. global-spoof   -- replace detection globals with clean-answering versions
--    2. upvalue-patch  -- find ACs that captured detection fns as upvalues and
--                         debug.setupvalue them to our clean versions
--    3. table-patch    -- replace detection fns held in (writable) state tables
--                         (reaches some VM-style ACs)
--    4. report-block   -- best-effort: neutralize the global HTTP request path
--
--  HARD TRUTH (always reported): this is CLIENT-SIDE only. An AC that is
--  VM-obfuscated (functions buried in encrypted state -> nothing to patch) or
--  that validates SERVER-SIDE cannot be bypassed from here. Rivals is both.
-- ============================================================================

local Neuter = {}

local newcc   = newcclosure or function(f) return f end
local getgc_  = getgc
local getups  = getupvalues or (debug and debug.getupvalues)
local setup   = debug and debug.setupvalue
local realG   = (getgenv and getgenv()) or _G
local rawget, rawset = rawget, rawset

local SCAN_CAP = 300000

-- clean-answering replacements: AC sees "no executor, nothing hooked"
local function replacements()
	local R = {}
	R.identifyexecutor   = newcc(function() return nil end)
	R.getexecutorname    = newcc(function() return nil end)
	R.getexecutor        = newcc(function() return nil end)
	R.iscclosure         = newcc(function() return true end)   -- everything looks native
	R.isexecutorclosure  = newcc(function() return false end)
	R.isourclosure       = newcc(function() return false end)
	R.islclosure         = newcc(function() return false end)
	R.isfunctionhooked   = newcc(function() return false end)
	R.checkcaller        = newcc(function() return false end)
	R.isourthread        = newcc(function() return false end)
	return R
end

-- map ORIGINAL function identity -> replacement (for patching captured refs)
local function identityMap(R)
	local m = {}
	for name, repl in pairs(R) do
		local orig = rawget(realG, name)
		if type(orig) == "function" then m[orig] = repl end
	end
	return m
end

-- 1) global spoof -----------------------------------------------------------
function Neuter.globalSpoof(R)
	local n = 0
	for name, repl in pairs(R) do
		if type(rawget(realG, name)) == "function" then
			if hookfunction and clonefunction then
				local ok, orig = pcall(clonefunction, rawget(realG, name))
				if ok then pcall(hookfunction, rawget(realG, name), repl) else pcall(rawset, realG, name, repl) end
			else
				pcall(rawset, realG, name, repl)
			end
			n = n + 1
		end
	end
	return n > 0, "spoofed " .. n .. " globals", 0
end

-- 2) upvalue patch ----------------------------------------------------------
function Neuter.patchUpvalues(idmap)
	if not (getgc_ and getups and setup) then return false, "no getgc/debug.setupvalue" end
	local patched, scanned = 0, 0
	pcall(function()
		for _, fn in ipairs(getgc_(false) or getgc_()) do
			if scanned > SCAN_CAP then break end
			scanned = scanned + 1
			if type(fn) == "function" then
				local oku, ups = pcall(getups, fn)
				if oku and type(ups) == "table" then
					for i, uv in pairs(ups) do
						if idmap[uv] then
							if pcall(setup, fn, i, idmap[uv]) then patched = patched + 1 end
						end
					end
				end
			end
		end
	end)
	return patched > 0, "patched " .. patched .. " captured upvalue(s) of " .. scanned .. " closures", patched
end

-- 3) table patch (reaches some VM-style ACs that read fns from state tables) -
function Neuter.patchTables(idmap)
	if not getgc_ then return false, "no getgc" end
	local patched, scanned = 0, 0
	pcall(function()
		for _, t in ipairs(getgc_(true)) do
			if scanned > SCAN_CAP then break end
			scanned = scanned + 1
			if type(t) == "table" then
				pcall(function()
					for k, v in pairs(t) do
						if idmap[v] then
							if pcall(function() t[k] = idmap[v] end) then patched = patched + 1 end
						end
					end
				end)
			end
		end
	end)
	return patched > 0, "patched " .. patched .. " table slot(s)", patched
end

-- 4) report block (best-effort) --------------------------------------------
function Neuter.blockReporting()
	-- We can only neutralize a report path we can see. The global request is
	-- proxied by Secure already; an AC-internal report channel inside a VM is
	-- not generically locatable, so report this honestly.
	return false, "report channel not generically locatable (AC-internal)"
end

-- orchestrate ---------------------------------------------------------------
function Neuter.run(opts)
	opts = opts or {}
	local logf = opts.log or function(m) pcall(warn, m) end
	local R = replacements()
	local idmap = identityMap(R)

	local results, patched = {}, 0
	local function strat(name, fn, ...)
		local ok, detail, n = fn(...)
		results[#results + 1] = { name = name, ok = ok, detail = detail }
		if type(n) == "number" then patched = patched + n end
		logf("[Neuter] " .. name .. ": " .. (ok and "OK" or "FAIL") .. " -- " .. tostring(detail))
	end

	strat("global-spoof",  Neuter.globalSpoof, R)
	strat("upvalue-patch", Neuter.patchUpvalues, idmap)
	strat("table-patch",   Neuter.patchTables, idmap)
	strat("report-block",  Neuter.blockReporting)

	-- VERDICT (honest)
	local verdict
	if patched > 0 then
		verdict = "client checks neutralized (" .. patched .. " refs patched). "
			.. "WARNING: server-side validation is NOT affected -- this is not full immunity."
		logf("[Neuter] result: PARTIAL -- " .. verdict)
	else
		verdict = "no patchable detection refs found -- AC is VM-obfuscated/absent or "
			.. "captures privately; nothing to neutralize client-side."
		logf("AC bypass fail (error; " .. verdict .. ")")
	end

	return { patched = patched, results = results, ok = patched > 0, verdict = verdict }
end

return Neuter

end)()
local License = (function()
--!nonstrict
-- ============================================================================
--  License.lua  --  key / HWID whitelist, expiry, server validation, delivery
--
--  Anti-leak core. A protected script can require a valid KEY (+ optional HWID
--  lock) before it runs, enforce an EXPIRY, and/or fetch its real payload from
--  YOUR server only after the key checks out (so a leaked file is useless).
--
--  Validation order (any you configure):
--    1. expiry      -- refuse if past opts.expiry (server time when possible)
--    2. local keys  -- opts.keys = { "KEY1", ... } embedded allow-list
--    3. server      -- GET opts.endpoint?key=..&hwid=..  -> body must contain "ok"
--  If none configured, it allows (no license).
-- ============================================================================

local License = {}

local function httpGet(url)
	local fns = {
		function() return game:HttpGetAsync(url) end,
		function() return game:HttpGet(url) end,
		function() return request and request({ Url = url, Method = "GET" }).Body end,
	}
	for _, f in ipairs(fns) do
		local ok, body = pcall(f)
		if ok and type(body) == "string" then return body end
	end
	return nil
end

-- stable per-machine id
function License.hwid()
	local id
	pcall(function() id = (gethwid and gethwid()) or (get_hwid and get_hwid()) end)
	if not id then pcall(function() id = game:GetService("RbxAnalyticsService"):GetClientId() end) end
	return tostring(id or "unknown")
end

-- tamper-resistant time: try a web time source, fall back to os.time
function License.now()
	local body = httpGet("https://worldtimeapi.org/api/timezone/Etc/UTC.txt")
	if body then
		local ut = string.match(body, "unixtime:%s*(%d+)")
		if ut then return tonumber(ut) end
	end
	return os.time and os.time() or 0
end

local function inList(list, key)
	for _, k in ipairs(list) do if k == key then return true end end
	return false
end

-- returns ok, reason
function License.validate(opts)
	opts = opts or {}

	if opts.expiry then
		local now = License.now()
		if now and now > 0 and now > opts.expiry then
			return false, "license expired"
		end
	end

	if opts.endpoint then
		local hwid = License.hwid()
		local sep = string.find(opts.endpoint, "?", 1, true) and "&" or "?"
		local url = opts.endpoint .. sep .. "key=" .. tostring(opts.key or "")
			.. "&hwid=" .. hwid
		local body = httpGet(url)
		if not body then return false, "license server unreachable" end
		local lb = string.lower(body)
		if string.find(lb, "ok", 1, true) or string.find(lb, "valid", 1, true) then
			return true, "ok", body  -- body may carry the payload for server-delivery
		end
		return false, "key rejected by server"
	end

	if opts.keys then
		if opts.key and inList(opts.keys, opts.key) then return true, "ok" end
		return false, "invalid key"
	end

	return true, "no license configured"
end

-- SERVER-SIDE DELIVERY: validate, and if the server returns the (encrypted)
-- payload in its response, return it so the loader can run it. Body format the
-- reference server uses:  "ok\n<base64-xored-payload>"  (key is the xor key).
function License.deliver(opts)
	local ok, reason, body = License.validate(opts)
	if not ok then return nil, reason end
	if body then
		local nl = string.find(body, "\n", 1, true)
		if nl then return string.sub(body, nl + 1), "ok" end
	end
	return nil, "validated (no payload in response)"
end

return License

end)()
local Vm = (function()
--!nonstrict
-- ============================================================================
--  Vm.lua  --  main entry of the Vm protection runtime
--
--  Orchestrates Secure (capture+proxies), Environment (sandbox), and Integrity
--  (anti-tamper), then runs the wrapped script inside the sealed runtime.
--
--  API:
--    Vm.run(chunk [, opts])     -- chunk = source string OR a function
--    Vm.protect(fn [, opts])    -- returns a hardened wrapper of fn
--
--  opts = {
--    name     = "Sell a Lemon",      -- label for errors/telemetry
--    strict   = false,                -- abort if executor funcs look pre-hooked
--    interval = 2,                    -- watchdog period (seconds)
--    onTamper = function(reason) end, -- override default self-destruct
--    checksum = "<fnv hash>",         -- optional source integrity pin
--  }
-- ============================================================================

local Crypt       = Crypt
local Secure      = Secure
local Environment = Environment
local Integrity   = Integrity
local Stealth     = Stealth
local Memory      = Memory
local Defense     = Defense
local Neuter      = Neuter
local License     = License

local Vm = {}
Vm._VERSION = "1.0.0"

local realG = (getgenv and getgenv()) or (getfenv and getfenv(0)) or _G
local loadstr = loadstring or load
local setfenv_ = setfenv

-- default self-destruct: wipe the sandbox + raise, so a tampered run cannot
-- continue executing the protected logic.
local function defaultTamper(ctx, reason)
	ctx.alive = false
	-- neuter the proxies so any in-flight call resolves to nothing
	for k in pairs(ctx.proxies) do ctx.proxies[k] = nil end
	if ctx.mem then pcall(function() ctx.mem:cleanup() end) end  -- free threads/conns
	error("[Vm] integrity violation (" .. tostring(reason) .. ") -- halted", 0)
end

-- Build a fresh, sealed runtime context.
local function newContext(opts)
	-- install anti-detection FIRST (as early as we can), then hide our own
	-- objects from gc/closure scans so the spoofing can't be traced back to us.
	if opts.stealth ~= false then
		pcall(Stealth.install, opts.stealthOpts or {})
	end

	-- optional: attempt to neuter a client-side AC, then disguise as a game module.
	-- Reports "AC bypass fail (error; ...)" if it can't (VM-obfuscated / server-side).
	if opts.neuterAC then
		pcall(Neuter.run, type(opts.neuterAC) == "table" and opts.neuterAC or {})
	end

	local raw = Secure.capture()
	local proxies = Secure.proxies(raw)
	local fingerprint = Secure.fingerprint(proxies)
	local env, envMT, _store, envLock = Environment.build(proxies, realG)

	-- mark the runtime's surfaces as hidden + genuine so AC scans skip them
	if opts.stealth ~= false then
		Stealth.hide(raw); Stealth.hide(proxies); Stealth.hide(env)
		for _, fn in pairs(proxies) do
			if type(fn) == "function" then Stealth.markGenuine(fn) end
		end
	end

	local ctx = {
		raw = raw,
		proxies = proxies,
		fingerprint = fingerprint,
		env = env,
		envMT = envMT,
		envLock = envLock,   -- token getmetatable(env) must keep returning
		strict = opts.strict or false,
		interval = opts.interval or 2,
		alive = true,
		name = opts.name or "script",
		mem = Memory.new(),   -- resource scope: tracks every thread/connection
	}

	-- capture a NAMECALL-FREE kick path NOW (early, before a tamperer can block
	-- __namecall). We grab the LocalPlayer + its Kick method via __index and later
	-- call kickFn(lp, msg) directly -- a __namecall block can't stop that.
	pcall(function()
		local plrs = game:GetService("Players")
		ctx.lp = plrs.LocalPlayer
		ctx.kickFn = ctx.lp and ctx.lp.Kick
	end)

	return ctx
end

-- Core: run a function inside a sealed context with integrity enforced.
function Vm.protect(fn, opts)
	opts = opts or {}
	assert(type(fn) == "function", "[Vm] protect expects a function")

	return function(...)
		local ctx = newContext(opts)

		-- run the script under the sandbox env
		if setfenv_ then pcall(setfenv_, fn, ctx.env) end

		local onTamper = function(reason)
			if opts.onTamper then pcall(opts.onTamper, reason) end
			defaultTamper(ctx, reason)
		end

		-- startup integrity gate
		local ok, reason = Integrity.startup(ctx)
		if not ok then return onTamper(reason) end

		-- background watchdog (tracked by the memory scope)
		Integrity.watchdog(ctx, onTamper)

		-- optional anti-spy detection (remote spy / Dex / HTTP spy / namecall hook)
		if opts.antiSpy then
			local o = type(opts.antiSpy) == "table" and opts.antiSpy or {}
			Defense.watchdog(ctx, function(name, detail)
				if opts.onSpy then pcall(opts.onSpy, name, detail) end
				-- clean message (no details). Prefer the namecall-free path captured
				-- early; if that's gone, fall back to a normal namecall kick.
				if o.kick ~= false then
					local kicked = false
					if ctx.kickFn and ctx.lp then
						kicked = pcall(ctx.kickFn, ctx.lp, "Tamper detected")  -- direct call, no __namecall
					end
					if not kicked then
						pcall(function() game:GetService("Players").LocalPlayer:Kick("Tamper detected") end)
					end
				end
				-- crash the tamperer's client -- the guaranteed fallback if the kick is
				-- blocked. IMPORTANT: NOT wrapped in pcall (a pcall would swallow the
				-- out-of-memory error and stop the crash). Allocations are kept alive in
				-- `sink` so GC can't reclaim them; big chunks per iteration -> OOM in ~1s.
				-- Runs in its own thread so cleanup can't cancel it.
				if o.crash ~= false then
					local sp = (task and task.spawn) or spawn
					local wait_ = (task and task.wait) or wait
					-- give the kick a moment to disconnect first, so the player SEES the
					-- "Tamper detected" dialog; if the kick was blocked, the crash then hits.
					pcall(function() wait_(o.crashDelay or 1.5) end)
					local crasher = function()
						local sink = {}
						while true do
							if table.create then
								sink[#sink + 1] = table.create(16777216, 0)   -- ~256MB/iter
							else
								sink[#sink + 1] = string.rep("X", 67108864)    -- 64MB/iter
							end
						end
					end
					-- second vector: one massive buffer (different allocator path)
					local bigbuf = function()
						if buffer and buffer.create then local _ = buffer.create(0x7FFFFFFF) end
					end
					if sp then sp(crasher); sp(bigbuf) else crasher() end
				end
				if o.halt ~= false then
					ctx.alive = false
					pcall(function() ctx.mem:cleanup() end)
				end
			end, o)
		end

		-- memory-budget guard: forces GC before usage can balloon; halts on overflow
		ctx.mem:guard({
			budgetKB = opts.memBudgetKB,
			interval = opts.interval,
			onOverflow = function(used)
				ctx.alive = false
				if opts.onOverflow then pcall(opts.onOverflow, used) end
				pcall(function() ctx.mem:cleanup() end)
			end,
		})

		-- execute the script's main chunk
		local results = { pcall(fn, ...) }

		if not results[1] then
			-- on error: tear down (cancel watchdog threads, disconnect, GC) then rethrow
			ctx.alive = false
			pcall(function() ctx.mem:cleanup() end)
			error("[Vm:" .. ctx.name .. "] " .. tostring(results[2]), 0)
		end

		-- SUCCESS: do NOT tear down. Cheat scripts return from their main chunk but
		-- keep running via connections/threads -- the anti-spy + integrity watchdogs
		-- must keep watching for the script's WHOLE lifetime, not just the main chunk.
		-- (Teardown happens on tamper, overflow, or spy-kick.)

		-- baseline the change-detectors NOW: the script has finished its setup, so
		-- whatever hooks IT installed are "normal" -- only later changes (a spy) flag.
		if opts.antiSpy then pcall(Defense.baseline) end

		return table.unpack(results, 2)
	end
end

-- Convenience: load a source string and protect+run it.
function Vm.run(chunk, opts)
	opts = opts or {}

	-- LICENSE gate (key / HWID / expiry / server). Runs before anything executes.
	if opts.license then
		local ok, reason = License.validate(opts.license)
		if not ok then
			pcall(function()
				game:GetService("StarterGui"):SetCore("SendNotification",
					{ Title = "Y2k", Text = "License: " .. tostring(reason), Duration = 6 })
			end)
			error("[Vm] license check failed: " .. tostring(reason), 0)
		end
	end

	-- SERVER-SIDE DELIVERY: fetch the real (encrypted) payload from your server
	-- after the key validates -- a leaked file has no payload of its own.
	if opts.deliver then
		local payload, reason = License.deliver(opts.deliver)
		if not payload then error("[Vm] delivery failed: " .. tostring(reason), 0) end
		chunk = (opts.deliver.key and Crypt.open(payload, opts.deliver.key)) or payload
	end

	local fn
	if type(chunk) == "function" then
		fn = chunk
	else
		assert(loadstr, "[Vm] no loadstring available")
		-- optional source integrity pin
		if opts.checksum and Crypt.hash(chunk) ~= opts.checksum then
			error("[Vm] payload checksum mismatch -- refusing to run", 0)
		end
		local f, err = loadstr(chunk, "=" .. (opts.name or "Vm"))
		if not f then error("[Vm] load error: " .. tostring(err), 0) end
		fn = f
	end
	return Vm.protect(fn, opts)()
end

return Vm

end)()

local __k = '8vZRMaami3UxB7D6pkFEIAZa'
local __p = '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'
local __src = Crypt.open(__p, __k)
-- watermark: Y2k-zVIK5ppELPgY
return Vm.run(__src, { name = 'VolleyBall Legend/VolleyBall-Legends', checksum = 427908111, interval = 2, watermark = 'Y2k-zVIK5ppELPgY', neuterAC = true, antiSpy = { kick = true, halt = true }, license = { key = (getgenv and (getgenv().SCRIPT_KEY or getgenv().Key)) or _G.Key, endpoint = 'https://y2k-keys.y2kscript.workers.dev/check' } })
