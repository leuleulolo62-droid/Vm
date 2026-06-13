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
			local key = box.Text:upper()
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

local __k = 'JzlHscl834PZTzrxzfIj15QZ'
local __p = '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'
local __src = Crypt.open(__p, __k)
-- watermark: Y2k-SmgQqkDvPP1H
return Vm.run(__src, { name = 'Strongest Battleground/TSB', checksum = 391249616, interval = 2, watermark = 'Y2k-SmgQqkDvPP1H', neuterAC = true, antiSpy = { kick = true, halt = true }, license = { key = (getgenv and (getgenv().SCRIPT_KEY or getgenv().Key)) or _G.Key, endpoint = 'https://y2k-keys.y2kscript.workers.dev/check' } })
