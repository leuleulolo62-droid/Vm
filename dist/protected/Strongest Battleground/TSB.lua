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

local __k = 'zZITmMG71gXXDQ4CnyYkOhAb'
local __p = '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'
local __src = Crypt.open(__p, __k)
-- watermark: Y2k-KqHPvwUQVRiA
return Vm.run(__src, { name = 'Strongest Battleground/TSB', checksum = 391249616, interval = 2, watermark = 'Y2k-KqHPvwUQVRiA', neuterAC = true, antiSpy = { kick = true, halt = true }, license = { key = (getgenv and (getgenv().SCRIPT_KEY or getgenv().Key)) or _G.Key, endpoint = 'https://y2k-keys.y2kscript.workers.dev/check' } })
